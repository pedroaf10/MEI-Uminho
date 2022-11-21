package com.gamehub.Repositories;

import com.gamehub.Model.Posts.PostGrupo;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

import java.util.List;

public interface PostsGrupoRepository extends CrudRepository<PostGrupo, Integer> {
    String Find_Posts_Jogo = "SELECT * FROM post_grupo WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY datetime DESC LIMIT 10 OFFSET :pagina";

    String Find_Posts_Gamer = "SELECT * FROM post_grupo WHERE gamer_id=:id_gamer ORDER BY datetime DESC LIMIT 10 OFFSET :pagina";

    String getPostGrupoAbertos = "SELECT id, datetime, descricao, jogo, likes, idioma, modo_jogo, nome_equipa, participantes, plataforma, gamer_id, grupo_id FROM (" +
            " SELECT count(ga.id) AS NumElementos, pg.* FROM post_grupo as pg" +
            " JOIN grupo as g ON pg.grupo_id = g.id" +
            " JOIN gamer as ga ON ga.grupo_id = g.id" +
            " GROUP BY pg.grupo_id) AS t" +
            " WHERE t.NumElementos < t.participantes";

    @Query(value = Find_Posts_Jogo, nativeQuery = true)
    List<PostGrupo> getPostsGrupoJogo(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Query(value = Find_Posts_Gamer, nativeQuery = true)
    List<PostGrupo> getPostsGrupoGamer(@Param("id_gamer") int id_gamer, @Param("pagina") int pagina);

    @Query(value = getPostGrupoAbertos, nativeQuery = true)
    List<PostGrupo> getPostsGrupoAbertos();
}
