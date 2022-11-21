package com.gamehub.Services;


import com.gamehub.Model.Posts.*;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Repositories.*;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Service
public class PostsService {

    @Autowired
    private PostsMultimediaRepository postsMultimediaRepository;
    @Autowired
    private PostsGrupoRepository postsGrupoRepository;
    @Autowired
    private GrupoRepository grupoRepository;
    @Autowired
    private TagRepository tagRepository;
    @Autowired
    private GamerRepository gamerRepository;

    /**
     * Obtém os posts multimédia para um determinado jogo para um jogador
     * @param id_gamer id do gamer a ver os posts
     * @param id_jogo id do jogo a pesquisar
     * @param pagina id do jogo a pesquisar
     * @return Uma lista de posts de uma determinada página com as reações fornecidas pelo gamer
     */
    public List<PostLike> getPostsMultimediaJogo(int id_gamer, int id_jogo, int pagina) {
        List<PostMultimedia> posts = this.postsMultimediaRepository.getPostsMultimediaJogo(id_jogo, pagina * 10);
        return getPostLikes(id_gamer, posts);
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
    public List<PostLike> getPostsMultimediaJogo(int id_gamer, int id_jogo, int pagina, String filtro, String ordem) {
        List<PostMultimedia> posts = new ArrayList<>();
        switch (filtro) {
            case("datetime") -> {
                switch (ordem.toUpperCase()) {
                    case ("ASC") -> {
                        posts = this.postsMultimediaRepository.getPostsMultimediaJogoDataDesc(id_jogo, pagina * 10);
                    }
                    case ("DESC") -> {
                            posts = this.postsMultimediaRepository.getPostsMultimediaJogoDataAsc(id_jogo, pagina * 10);
                    }
                }
            }
            case("likes") -> {
                switch (ordem.toUpperCase())
                {
                    case ("ASC") ->
                    {
                        posts = this.postsMultimediaRepository.getPostsMultimediaJogoLikesAsc(id_jogo, pagina * 10);
                    }
                    case ("DESC") ->
                    {
                        posts = this.postsMultimediaRepository.getPostsMultimediaJogoLikesDesc(id_jogo, pagina * 10);
                    }
                }
            }

        }

        return getPostLikes(id_gamer, posts);
    }

    /**
     * Método que devolve uma lista de posts com reações dado um gamer e a lista de posts.
     * @param id_gamer id do gamer
     * @param posts lista de posts
     * @return Lista dos posts já com as reações do gamer
     */
    private List<PostLike> getPostLikes(int id_gamer, List<PostMultimedia> posts)
    {
        int reacao;
        List<PostLike> resultado = new ArrayList<>();


        for (PostMultimedia post : posts) {
            reacao = this.postsMultimediaRepository.getLike(post.getId(), id_gamer).intValue();
            if (reacao == 1) {
                resultado.add(new PostLike(post.getId(), post.getLikes(), post.getDatetime(), post.getJogo(), post.getDescricao(), post.getTags(), post.getMultimedia(), post.getGamer(), "like"));
            } else {
                reacao = this.postsMultimediaRepository.getDislike(post.getId(), id_gamer).intValue();
                if (reacao == 1) {
                    resultado.add(new PostLike(post.getId(), post.getLikes(), post.getDatetime(), post.getJogo(), post.getDescricao(), post.getTags(), post.getMultimedia(), post.getGamer(), "dislike"));
                } else
                    resultado.add(new PostLike(post.getId(), post.getLikes(), post.getDatetime(), post.getJogo(), post.getDescricao(), post.getTags(), post.getMultimedia(), post.getGamer(), "neutro"));
            }

        }

        return resultado;
    }

    /**
     * Obter os posts de grupo para um determinado jogo
     * @param id_jogo id do jogo pretendido
     * @param pagina página pretendida
     * @return lista dos posts de grupo correspondentes
     */
    public List<PostGrupo> getPostsGrupoJogo(int id_jogo, int pagina) {
        return this.postsGrupoRepository.getPostsGrupoJogo(id_jogo, pagina * 10);
    }

    /**
     * Remove like de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    public void removeLike(int id_post, int id_gamer) {
        this.postsMultimediaRepository.removeLikePost(id_post, id_gamer);
        this.postsMultimediaRepository.update_dislikesPost(id_post);
    }

    /**
     * Remove dislike de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    public void removeDislike(int id_post, int id_gamer) {
        this.postsMultimediaRepository.removeDislikePost(id_post, id_gamer);
        this.postsMultimediaRepository.update_likesPost(id_post);
    }

    /**
     * Insere like de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    public void likePost(int id_post, int id_gamer) {
        try {
            this.postsMultimediaRepository.removeDislikePost(id_post, id_gamer);
        } catch (Exception e) {
            System.out.println("Não havia dislike deste utilizador!");
        }

        this.postsMultimediaRepository.likePost(id_post, id_gamer);
        this.postsMultimediaRepository.update_likesPost(id_post);
    }

    /**
     * Insere dislike de um gamer num determinado posts
     * @param id_post id do post
     * @param id_gamer id do post
     */
    public void dislikePost(int id_post, int id_gamer) {
        try {
            this.postsMultimediaRepository.removeLikePost(id_post, id_gamer);
        } catch (Exception e) {
            System.out.println("Não havia like deste utilizador!");
        }

        this.postsMultimediaRepository.dislikePost(id_post, id_gamer);
        this.postsMultimediaRepository.update_dislikesPost(id_post);
    }

    /**
     * Insere um post, quer seja de grupo ou multimédia
     * @param post post a ser inserido
     */
    public void insertPost(Post post) {
        if (post instanceof PostMultimedia) {
            this.postsMultimediaRepository.save((PostMultimedia) post);
        } else {
            this.postsGrupoRepository.save((PostGrupo) post);
        }
    }

    /**
     * Inserir novo grupo
     * @param grupo grupo a ser inserido
     */
    public void insertGrupo(Grupo grupo) {
        this.grupoRepository.save(grupo);
    }

    /**
     * Eliminar um post dado o seu id
     * @param id_post identificador do post
     * @param tipo_post 0 se for do tipo multimédia, 1 se for do tipo grupo
     */
    public void deletePost(int id_post, int tipo_post) {

        if (tipo_post == 0) {
            this.postsMultimediaRepository.deleteDislikesFromPost(id_post);
            this.postsMultimediaRepository.deleteLikesFromPost(id_post);
            this.postsMultimediaRepository.deletePostMultimediaTags(id_post);
            this.postsMultimediaRepository.deleteById(id_post);
            // trabalho futuro: apagar a media na API
        } else {
            this.gamerRepository.removeFromGroup(id_post);
            this.postsGrupoRepository.deleteById(id_post);
        }
    }

    /**
     * Obter as pessoas de um determinado grupo
     * @param idGrupo id do grupo
     * @return Os gamers que se encontram no grupo
     */
    public List<Gamer> getPessoasGrupo(int idGrupo) {
        List<Gamer> gamers = new ArrayList<>();
        Optional<Grupo> res = grupoRepository.findById(idGrupo);
        if (res.isPresent()) {
            Grupo grupo = res.get();
            gamers = grupo.getGamers();
        }
        return gamers;
    }

    /**
     * Obter um grupo dado o seu id
     * @param id id do grupo
     * @return o grupo encontrado
     */
    public Grupo get_grupo_by_id(int id) {
        return this.grupoRepository.findById(id).orElse(null);
    }

    /**
     * Adicionar um participante a um grupo
     * @param gamer Gamer a ser inserido
     * @param id_grupo id do grupo ao qual inserir
     */
    public void add_participante_grupo(Gamer gamer, int id_grupo) {
        Grupo g = this.get_grupo_by_id(id_grupo);
        g.add_participante(gamer);
        this.grupoRepository.save(g);
    }

    /**
     * Obter o grupo de um determinado post grupo dado o id do post grupo
     * @param id_post_grupo id do post grupo
     * @return
     */
    public Grupo get_Grupo_by_post(int id_post_grupo) {

        Grupo g = null;

        Optional<PostGrupo> opg = this.postsGrupoRepository.findById(id_post_grupo);
        if (opg.isPresent()) {
            PostGrupo pg = opg.get();
            g = pg.getGrupo();
        }

        return g;
    }

    /**
     * Encontra os posts grupo de um determinado gamer
     * @param id_gamer id do gamer
     * @param pagina pagina dos posts
     * @return Lista de posts grupo de um determinado gamer
     */
    public List<PostGrupo> getPostsGrupoGamer(int id_gamer, int pagina) {
        return this.postsGrupoRepository.getPostsGrupoGamer(id_gamer, pagina * 10);
    }

    /**
     * Encontra os posts multimedia de um determinado gamer
     * @param id_gamer id do gamer
     * @param pagina pagina dos posts
     * @return Lista de posts multimedia de um determinado gamer
     */
    public List<PostMultimedia> getPostsMediaGamer(int id_gamer, int pagina) {
        return this.postsMultimediaRepository.getPostsMultimediaGamer(id_gamer, pagina * 10);
    }

    /**
     * Obter as tags disponiveis de momento
     * @return lista de tags disponíveis
     */
    public List<Tag> getTagsDisponiveis() {
        List<Tag> resultado = new ArrayList<>();
        tagRepository.findAll().forEach(t-> {
            if(!t.getTag().equals("NEWS"))
                resultado.add(t);
        });
        return resultado;
    }

    /**
     * Obter uma tag dado o seu id
     * @param id da tag
     * @return a tag encontrada
     */
    public Tag get_tag_by_id(int id) {
        Optional<Tag> otg = this.tagRepository.findById(id);
        return otg.orElse(null);
    }

    /**
     * Obter todos os postgrupo disponíveis
     * @return lista de posts de grupo
     */
    public List<PostGrupo> getPostsGrupo() {
        return this.postsGrupoRepository.getPostsGrupoAbertos();
    }

    /**
     * Apaga um grupo caso já não exista nenhum membro dentro dele.
     * @param id_grupo id do grupo
     */
    public void apagar_grupo_se_vazio(int id_grupo) {
        Optional<Grupo> og = this.grupoRepository.findById(id_grupo);
        if (og.isPresent()) {
            Grupo g = og.get();
            int num_elem = this.grupoRepository.getNumElementosGrupo(g.getId());
            if (num_elem <= 0) {
                this.grupoRepository.delete(g);
            }
        }
    }

    /**
     * Obter os posts multimedia mais populares
     * @param limit o número de posts pretendido
     * @param id_gamer id do gamer para obter as suas reações
     * @return Lista dos posts multimedia com a reação do gamer
     */
    public List<PostLike> getPostsMultimedia(int limit, int id_gamer) {
        List<PostMultimedia> posts= this.postsMultimediaRepository.getPostsMultimediaTOP(limit);

        return getPostLikes(id_gamer,posts);
    }

    /**
     * Obter todos os posts multimedio
     * @return lista de todos os posts multimedia
     */
    public List<PostMultimedia> getTodosPostsMultimedia() {
        return this.postsMultimediaRepository.getTodosPostsMultimedia();
    }

    /**
     * Obter os posts multimedia de um determinado amigo
     * @param id_gamer id do gamer
     * @param id_amigo id gamer do amigo
     * @param pagina id da pagina pretendida
     * @return lista dos posts com as reações do gamer
     */
    public List<PostLike> getPostsMultimediaAmigo(int id_gamer, int id_amigo, int pagina)
    {
        List<PostMultimedia> posts = this.getPostsMediaGamer(id_amigo,pagina);
        return getPostLikes(id_gamer,posts);
    }
}
