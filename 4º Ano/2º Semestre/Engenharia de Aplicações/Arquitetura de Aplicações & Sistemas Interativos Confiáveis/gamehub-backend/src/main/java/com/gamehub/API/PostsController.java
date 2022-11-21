package com.gamehub.API;


import com.gamehub.Model.JSON.JogosPopularesJSON;
import com.gamehub.Model.JSON.PostJSON;
import com.gamehub.Model.Posts.*;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Services.GamerService;
import com.gamehub.Services.JogoService;
import com.gamehub.Services.PostsService;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.*;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

@CrossOrigin
@RequestMapping("api/v1/posts")
@RestController
public class PostsController {

    private final PostsService postsService;
    private final GamerService gamerService;
    private final JogoService jogoService;


    @Autowired
    public PostsController(PostsService postsService, GamerService gs, JogoService js) {
        this.postsService = postsService;
        this.gamerService = gs;
        this.jogoService = js;
    }

    /**
     * Obtém os posts multimédia para um determinado jogo para um jogador
     * @param id_gamer id do gamer a ver os posts
     * @param id_jogo id do jogo a pesquisar
     * @param pagina id do jogo a pesquisar
     * @return Uma lista de posts de uma determinada página com as reações fornecidas pelo gamer
     */
    @RequestMapping("/multimedia/{id_gamer}/{id_jogo}/{pagina}")
    @GetMapping
    public List<PostLike> getPostsMultimediaJogo(@PathVariable(value = "id_gamer") int id_gamer,
                                                 @PathVariable(value = "id_jogo") int id_jogo,
                                                 @PathVariable(value = "pagina") int pagina) {
        return this.postsService.getPostsMultimediaJogo(id_gamer, id_jogo, pagina);
    }

    /**
     * Obter os posts multimedia de um determinado amigo
     * @param id_gamer id do gamer
     * @param id_amigo id gamer do amigo
     * @param pagina id da pagina pretendida
     * @return lista dos posts com as reações do gamer
     */
    @RequestMapping("/multimedia/postAmigo/{id_gamer}/{id_amigo}/{pagina}")
    @GetMapping
    public List<PostLike> getPostsMultimediaAmigo(@PathVariable(value = "id_gamer") int id_gamer,
                                                 @PathVariable(value = "id_amigo") int id_amigo,
                                                 @PathVariable(value = "pagina") int pagina) {
        return this.postsService.getPostsMultimediaAmigo(id_gamer, id_amigo, pagina);
    }

    /**
     * Obtém os posts multimédia para um determinado jogo para um jogador, só que desta vez filtrado
     * @param id_gamer id do gamer a ver os posts
     * @param id_jogo id do jogo a pesquisar
     * @param pagina id do jogo a pesquisar
     * @param filtro filtro pretendido
     * @param ordem ordenação fornecida
     * @return Uma lista de posts de uma determinada página filtrada, com as reações fornecidas pelo gamer
     */
    @RequestMapping("/multimedia/{id_gamer}/{id_jogo}/{pagina}/{filtro}/{ordem}")
    @GetMapping
    public List<PostLike> getPostsMultimediaJogo(@PathVariable(value = "id_gamer") int id_gamer,
                                                 @PathVariable(value = "id_jogo") int id_jogo,
                                                 @PathVariable(value = "pagina") int pagina,
                                                 @PathVariable(value = "filtro") String filtro,
                                                 @PathVariable(value = "ordem") String ordem) {
        System.out.println(filtro);
        return this.postsService.getPostsMultimediaJogo(id_gamer, id_jogo, pagina, filtro, ordem);
    }

    /**
     * Obter os posts de grupo para um determinado jogo
     * @param id_jogo id do jogo pretendido
     * @param pagina página pretendida
     * @return lista dos posts de grupo correspondentes
     */
    @RequestMapping("/grupo/{id_jogo}/{pagina}")
    @GetMapping
    public List<PostGrupo> getPostsGrupoJogo(@PathVariable(value = "id_jogo") int id_jogo, @PathVariable(value = "pagina") int pagina) {
        return this.postsService.getPostsGrupoJogo(id_jogo, pagina);
    }

    /**
     * Remove like de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    @RequestMapping("/like/remove/{id_post}/{id_gamer}")
    @PostMapping
    public void removeLikePost(@PathVariable(value = "id_post") int id_post, @PathVariable(value = "id_gamer") int id_gamer) {
        this.postsService.removeLike(id_post, id_gamer);
    }

    /**
     * Remove dislike de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    @RequestMapping("/dislike/remove/{id_post}/{id_gamer}")
    @PostMapping
    public void removeDislikePost(@PathVariable(value = "id_post") int id_post, @PathVariable(value = "id_gamer") int id_gamer) {
        this.postsService.removeDislike(id_post, id_gamer);
    }

    /**
     * Insere like de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    @RequestMapping("/like/{id_post}/{id_gamer}")
    @PostMapping
    public void likePost(@PathVariable(value = "id_post") int id_post, @PathVariable(value = "id_gamer") int id_gamer) {
        this.postsService.likePost(id_post, id_gamer);
    }

    /**
     * Insere dislike de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    @RequestMapping("/dislike/{id_post}/{id_gamer}")
    @PostMapping
    public void dislikePost(@PathVariable(value = "id_post") int id_post, @PathVariable(value = "id_gamer") int id_gamer) {
        this.postsService.dislikePost(id_post, id_gamer);
    }


    /**
     * Criar um post multimédia
     * @param pj PostJason
     * @param id_gamer id do gamer
     * @return id do post multimédia
     */
    @RequestMapping("/createPostMedia/{id}")
    @PostMapping
    public int create_post_media(@RequestBody PostJSON pj, @PathVariable(value = "id") int id_gamer) {
        Gamer gamer = gamerService.getGamerById(id_gamer);
        List<Tag> temp = new ArrayList<>();
        for (Integer id_tag : pj.getTags()) {
            temp.add(postsService.get_tag_by_id(id_tag));
        }
        PostMultimedia p = new PostMultimedia(pj.getJogo(), pj.getDescricao(), 0, LocalDateTime.now(), pj.getMultimedia(), gamer, temp);
        this.postsService.insertPost(p);
        return p.getId();
    }

    /**
     * Criar um post grupo
     * @param pj PostJason
     * @param id_gamer id do gamer
     * @return id do post grupo
     */
    @RequestMapping("/createPostGrupo/{id}")
    @PostMapping
    public int create_post_grupo(@RequestBody PostJSON pj, @PathVariable(value = "id") int id_gamer) {
        Gamer gamer = gamerService.getGamerById(id_gamer);
        List<Gamer> participantes_grupo = new ArrayList<>();
        participantes_grupo.add(gamer);

        String link = this.jogoService.getLinkBannerJogo(pj.getJogo());

        Grupo grupo = new Grupo(participantes_grupo, link);
        PostGrupo p = new PostGrupo(0, LocalDateTime.now(), pj.getJogo(), pj.getDescricao(), pj.getIdioma(), pj.getModoJogo(), pj.getParticipantes(), pj.getNomeEquipa(), pj.getPlataforma(), gamer, grupo);
        grupo.setPostGrupo(p);

        this.postsService.insertGrupo(grupo);
        this.postsService.insertPost(p);

        gamer.setGrupo(grupo);
        this.gamerService.insertGamer(gamer);
        return p.getId();
    }

    /**
     * Eliminar um post dado o seu id
     * @param id_post identificador do post
     * @param tipo_post 0 se for do tipo multimédia, 1 se for do tipo grupo
     */
    @RequestMapping("/deletePost/{id_post}")
    @PostMapping
    public boolean apagar_post(@PathVariable(value = "id_post") int id_post, @RequestParam(defaultValue = "tipo_post") int tipo_post) {
        this.postsService.deletePost(id_post, tipo_post);
        return true;
    }

    /**
     * Encontra os posts grupo de um determinado gamer
     * @param id_gamer id do gamer
     * @param pagina pagina dos posts
     * @return Lista de posts grupo de um determinado gamer
     */
    @RequestMapping("/postsGrupoGamer/{id}/{pagina}")
    @GetMapping
    public List<PostGrupo> getPostsGrupoGamer(@PathVariable(value = "id") int id_gamer, @PathVariable(value = "pagina") int pagina) {
        return this.postsService.getPostsGrupoGamer(id_gamer, pagina);
    }

    /**
     * Encontra os posts multimedia de um determinado gamer
     * @param id_gamer id do gamer
     * @param pagina pagina dos posts
     * @return Lista de posts multimedia de um determinado gamer
     */
    @RequestMapping("/postsMediaGamer/{id}/{pagina}")
    @GetMapping
    public List<PostMultimedia> getPostsMediaGamer(@PathVariable(value = "id") int id_gamer, @PathVariable(value = "pagina") int pagina) {
        return this.postsService.getPostsMediaGamer(id_gamer, pagina);
    }

    /**
     * Obter as tags disponiveis de momento
     * @return lista de tags disponíveis
     */
    @RequestMapping("/getTags")
    @GetMapping
    public List<Tag> getTags() {
        return this.postsService.getTagsDisponiveis();
    }

    /**
     * Obter todos os postgrupo disponíveis
     * @return lista de posts de grupo
     */
    @RequestMapping("/postsGrupo")
    @GetMapping
    public List<PostGrupo> getPostsGrupo() {
        return this.postsService.getPostsGrupo();
    }

    /**
     * Obter os posts multimedia mais populares
     * @param limit o número de posts pretendido
     * @param id_gamer id do gamer para obter as suas reações
     * @return Lista dos posts multimedia com a reação do gamer
     */
    @RequestMapping("/postsMultimedia/{limit}/{id_gamer}")
    @GetMapping
    public List<PostLike> getPostsMultimedia(@PathVariable(value = "limit") int limit, @PathVariable(value="id_gamer") int id_gamer) {
        return this.postsService.getPostsMultimedia(limit,id_gamer);
    }

    /**
     * Método responsável por obter os jogos mais populares. Ou seja os jogos mais seguidos
     * @param limit Define o TOP-limit a encontrar. Por exemplo, se limit=4 será o TOP-4.
     * @return Retorna a lista com os jogos mais seguidos + a informação de quantos seguidores tem cada jogo.
     */
    @RequestMapping("/getListaJogosPopulares")
    @GetMapping
    public List<JogosPopularesJSON> get_lista_jogos_populares(@RequestParam(defaultValue = "limit") int limit) {
        return jogoService.getJogosPopulares(limit);
    }

    /**
     * Obter todos os posts multimedio
     * @return lista de todos os posts multimedia
     */
    @RequestMapping("/postsMultimedia")
    @GetMapping
    public List<PostMultimedia> getPostsMultimedia() {
        return this.postsService.getTodosPostsMultimedia();
    }

}
