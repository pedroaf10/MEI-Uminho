package com.gamehub.Tasks;


import com.gamehub.Model.Posts.Jogo;
import com.gamehub.Model.Posts.PostMultimedia;
import com.gamehub.Model.Posts.Tag;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Repositories.GamerRepository;
import com.gamehub.Repositories.JogoRepository;
import com.gamehub.Repositories.PostsMultimediaRepository;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.scheduling.annotation.EnableScheduling;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Component;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ThreadLocalRandom;


@EnableScheduling
@Component
public class NewsTask {

    @Value("${deploymentNumber}")
    private String deploymentNumber;
    @Autowired
    private JogoRepository jogoRepository;

    @Autowired
    private GamerRepository gamerRepository;

    @Autowired
    PostsMultimediaRepository postsMultimediaRepository;


    /**
     * Método responsável por de 24 em 24 horas obter as noticias do jogos
     * @throws IOException caso existam erros
     */
    @Scheduled(fixedDelay = 86400000)
    public void scheduleFixedDelayTask() throws IOException {
        if(deploymentNumber.equals("0")) {
            List<Jogo> jogos = new ArrayList<>();
            jogoRepository.findAll().forEach(jogos::add);

            Gamer gamehub = gamerRepository.findById(1).orElse(null);

            if (gamehub != null) {
                for (Jogo j : jogos) {
                    StringBuilder sb = new StringBuilder();
                    sb.append("https://newsapi.org/v2/everything?");
                    sb.append("qInTitle=");
                    sb.append(j.getNome().replace(" ", "%20"));
                    sb.append("&from=");
                    DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd");

                    LocalDate data_ontem = LocalDate.now().minusDays(15);
                    LocalDate data_atual = LocalDate.now();
                    sb.append(formatter.format(data_ontem));
                    sb.append("&to=");
                    sb.append(formatter.format(data_atual));
                    sb.append("&sortBy=popularity&language=en&apiKey=76f9ef4fa35d4ed5991a3c669e57c9d1");


                    URL url = new URL(sb.toString());
                    HttpURLConnection con = (HttpURLConnection) url.openConnection();
                    con.setRequestMethod("GET");


                    int status = con.getResponseCode();

                    BufferedReader in = new BufferedReader(
                            new InputStreamReader(con.getInputStream()));
                    String inputLine;
                    StringBuffer content = new StringBuffer();
                    while ((inputLine = in.readLine()) != null) {
                        content.append(inputLine);
                    }
                    in.close();

                    List<PostMultimedia> posts = this.parse(content.toString(), j.getNome(), gamehub);

                    this.postsMultimediaRepository.saveAll(posts);
                }

            }
        }



    }

    /**
     * Método responsaável por receber uma resposta e criar as noticias de um determinado jogo
     * @param responseBody Resposta da API
     * @param jogo Nome do jogo que verificou
     * @param gamer Gamer "GameHub" que irá publicar as noticias
     * @return Lista com as publicações das noticias a realizar
     * @throws JSONException caso ocorram errsos
     */
    public List<PostMultimedia> parse(String responseBody, String jogo, Gamer gamer) throws JSONException {
        JSONObject json = new JSONObject(responseBody);
        List<PostMultimedia> data = new ArrayList<>();
        JSONArray articles = json.getJSONArray("articles");

        for (int i = 0; i < articles.length(); i++) {

            JSONObject artigo = articles.getJSONObject(i);
            JSONObject source = artigo.getJSONObject("source");

            String source_name = source.getString("name");


            String author;
            try {
                author = artigo.getString("author");
            } catch (Exception e) {
                author = "Autor desconhecido";
            }

            String title = artigo.getString("title");
            String description = artigo.getString("description");
            String url = artigo.getString("url");

            String urlImage;
            try {
                urlImage = artigo.getString("urlToImage");
            } catch (Exception e) {
                urlImage = null;
            }


            DateTimeFormatter dt = DateTimeFormatter.ofPattern("yyyy-MM-dd'T'HH:mm:ss'Z'");
            LocalDateTime publishedAt = LocalDateTime.parse(artigo.getString("publishedAt"), dt);

            List<Tag> tags = new ArrayList<>();
            tags.add(new Tag(1, "NEWS", "NEWS"));

            StringBuilder sb = new StringBuilder();
            sb.append(title);
            sb.append("\n");
            sb.append(url);
            sb.append("\n");
            sb.append(author);
            sb.append("\n");
            sb.append(source_name);
            sb.append("\n");

            String content = sb.toString();


            data.add(new PostMultimedia(jogo,
                    content,
                    ThreadLocalRandom.current().nextInt(-10, 150 + 1),
                    publishedAt,
                    (urlImage == null) ? "" : urlImage,
                    gamer,
                    tags));
        }

        return data;
    }
}
